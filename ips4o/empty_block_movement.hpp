/******************************************************************************
 * ips4o/empty_block_movement.hpp
 *
 * In-place Parallel Super Scalar Samplesort (IPS⁴o)
 *
 ******************************************************************************
 * BSD 2-Clause License
 *
 * Copyright © 2017, Michael Axtmann <michael.axtmann@kit.edu>
 * Copyright © 2017, Daniel Ferizovic <daniel.ferizovic@student.kit.edu>
 * Copyright © 2017, Sascha Witt <sascha.witt@kit.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *****************************************************************************/

#pragma once

#include <algorithm>

#include "ips4o_fwd.hpp"
#include "memory.hpp"

namespace ips4o {
namespace detail {

/**
 * Moves empty blocks to establish invariant:
 * All buckets must consist of full blocks followed by empty blocks.
 */
template <class Cfg>
void Sorter<Cfg>::moveEmptyBlocks(const diff_t my_begin, const diff_t my_end,
                                  const diff_t my_first_empty_block) {
    // Find range of buckets that start in this stripe
    const int bucket_range_start = [&](int i) {
        while (Cfg::alignToNextBlock(bucket_start_[i]) < my_begin) ++i;
        return i;
    }(0);
    const int bucket_range_end = [&](int i) {
        const auto num_buckets = num_buckets_;
        if (my_id_ == num_threads_ - 1) return num_buckets;
        while (i < num_buckets && Cfg::alignToNextBlock(bucket_start_[i]) < my_end) ++i;
        return i;
    }(bucket_range_start);

    /*
     * After classification, a stripe consists of full blocks followed by empty blocks.
     * This means that the invariant above already holds for all buckets except those that
     * cross stripe boundaries.
     *
     * The following cases exist:
     * 1)  The bucket is fully contained within one stripe.
     *     In this case, nothing needs to be done, just set the bucket pointers.
     *
     * 2)  The bucket starts in stripe i, and ends in stripe i+1.
     *     In this case, thread i moves full blocks from the end of the bucket (from the
     *     stripe of thread i+1) to fill the holes at the end of its stripe.
     *
     * 3)  The bucket starts in stripe i, crosses more than one stripe boundary, and ends in stripe i+k.
     *     This is an extension of case 2. In this case, multiple threads work on the same bucket.
     *     Each thread is responsible for filling the empty blocks in its stripe.
     *     The left-most thread will take the right-most blocks. Therefore, we count how
     *     many blocks are fetched by threads to our left before moving our own blocks.
     */

    // Check if last bucket overlaps the end of the stripe
    const auto bucket_end = Cfg::alignToNextBlock(bucket_start_[bucket_range_end]);
    const bool last_bucket_is_overlapping = bucket_end > my_end;

    // Case 1)
    for (int b = bucket_range_start; b < bucket_range_end - last_bucket_is_overlapping; ++b) {
        const auto start = Cfg::alignToNextBlock(bucket_start_[b]);
        const auto stop = Cfg::alignToNextBlock(bucket_start_[b + 1]);
        auto read = stop;
        if (my_first_empty_block <= start) {
            // Bucket is completely empty
            read = start;
        } else if (my_first_empty_block < stop) {
            // Bucket is partially empty
            read = my_first_empty_block;
        }
        bucket_pointers_[b].set(start, read - Cfg::kBlockSize);
    }

    // Cases 2) and 3)
    if (last_bucket_is_overlapping) {
        const int overlapping_bucket = bucket_range_end - 1;
        const auto bucket_start = Cfg::alignToNextBlock(bucket_start_[overlapping_bucket]);

        // If it is a very large bucket, other threads will also move blocks around in it (case 3)
        diff_t blocks_reserved = 0;
        if (bucket_start < my_begin) {
            int prev_id = my_id_ - 1;
            do {
                const auto eb = shared_->local[prev_id]->first_empty_block;
                blocks_reserved += shared_->local[prev_id + 1]->first_block - std::max(eb, bucket_start);
            } while (prev_id-- && bucket_start < shared_->local[prev_id + 1]->first_block);
        }

        // Find stripe which contains last block of this bucket
        // Off by one because it is decreased in updateReadPointers
        int read_from_thread = my_id_;
        while (read_from_thread < num_threads_
               && bucket_end > shared_->local[read_from_thread]->first_block)
            ++read_from_thread;

        // write_ptr points to first empty block in this bucket
        auto write_ptr = begin_ + std::max(my_first_empty_block, bucket_start);
        const auto write_ptr_end = begin_ + my_end;

        // read_ptr goes right-to-left
        diff_t read_ptr = -1, read_ptr_end = 0;
        const auto updateReadPointers = [&] {
            // Find next block to read in previous stripe when the current stripe is empty
            while (read_ptr <= read_ptr_end) {
                --read_from_thread;
                read_ptr = std::min(shared_->local[read_from_thread]->first_empty_block, bucket_end)
                           - Cfg::kBlockSize;
                read_ptr_end = shared_->local[read_from_thread]->first_block - Cfg::kBlockSize;
                if (read_from_thread == my_id_) return false;
            }
            return true;
        };

        // Read pointer will get updated one more time after last block has been written
        while (updateReadPointers() && write_ptr < write_ptr_end) {
            // Skip reserved blocks
            if (blocks_reserved >= (read_ptr - read_ptr_end)) {
                blocks_reserved -= (read_ptr - read_ptr_end);
                read_ptr = read_ptr_end;
                continue;
            }
            read_ptr -= blocks_reserved;
            blocks_reserved = 0;
            // Move blocks from end of bucket into gap
            while (read_ptr > read_ptr_end && write_ptr < write_ptr_end) {
                std::move(begin_ + read_ptr, begin_ + read_ptr + Cfg::kBlockSize, write_ptr);
                read_ptr -= Cfg::kBlockSize;
                write_ptr += Cfg::kBlockSize;
            }
        }

        /* Set bucket pointers if the last filled block in the bucket is in our stripe.
         * There are 4 cases:
         * 1)  We filled our empty blocks, and there are no more filled blocks to our right.
         * 2)  We filled our empty blocks, there are some more filled blocks to our right,
         *     and the bucket ends in the next stripe.
         * 3)  We didn't fill all our empty blocks, but we wrote at least one filled block.
         *     This means that we own the last filled block in the bucket.
         * 4)  We didn't do anything, and we are the left-most thread.
         *     This means no one else did anything, either.
         */
        if (write_ptr == write_ptr_end) {
            if (read_from_thread == my_id_) {
                // Case 1)
                bucket_pointers_[overlapping_bucket].set(bucket_start, write_ptr - begin_ - Cfg::kBlockSize);
            } else if (read_from_thread == my_id_ + 1) {
                // Case 2)
                bucket_pointers_[overlapping_bucket].set(bucket_start, read_ptr);
            }
        } else if (write_ptr - begin_ > std::max(my_first_empty_block, bucket_start) || bucket_start >= my_begin) {
            // Case 3) or Case 4)
            bucket_pointers_[overlapping_bucket].set(bucket_start, write_ptr - begin_ - Cfg::kBlockSize);
        }
    }
}

}  // namespace detail
}  // namespace ips4o
