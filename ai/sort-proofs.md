Your task is to improve the organization of the dataplane folder.
We need a good big plan for it:
First, make a sort of dependency tree of the folder.
The main two files that we want working in the end are the two
examples: Label_Propagation_op_Correctness.thy and Batch_op_Correctness.thy.
These are the two files that need to always check after any sorting of code.

I think the better strategy for the plan is to start from the more root files (e.g. files that are the base theory, and important by others). For example,
the files with the name starting with Timely_ prefix are things that
are related to the Timely Dataflow infrastructure formalization. These probable
should be even in a separated folder.
So it can be very nice to move things to separate folder if it makes the organization
more clean.

Another point to this organization is to have a things inside of files also organized.
So it is not only organization between files, but within the files themselves.
For that, you will group the lemmas and definitions by similarity (e.g. they are related).
Create isabelle sections with short text descriptions of the lemmas and definitions in the section.

There are two main goals for this dataplane folder sorting:
1. Improve overall organization, so things are in places that make sense.
2. Improve the parallelism of the isabelle checker by having things split into separate file that can be check in parallel. Overall, improving the dependency tree structure so things can be check faster.

So for now, I just want you to come up with a plan on how to organize the dataplane
folder. Study the dependencies of those two mentioned files, and make sure that
the sorting plan can keep things working.
I will review your plan and ask you to write it down here, so we
can keep track of the progress of the plan during its execution.


Important for the plan execution:
Move all lemmas at once, and use the MCP connection to check if the edit was successful.
Keep checking if things are still working after the move. In particular,
if those two files still check completely.
