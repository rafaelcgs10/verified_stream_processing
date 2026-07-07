Your task is to improve the organization of the dataplane folder.
There are many lemmas out of place, in files that make no sense. There were placed there because during the process of proving, it was faster to just place them there.
But now I want to find better places for them. We will work in on file at the time. We will start with the Examples/Batch_op_Correctness.thy first.
I want you to scan this file and find lemmas that look out of place. In particular, look for comments with FIXME: move me, they indicate that the lemma should be somewhere else.
Investigate the dataplane structure to find good places for the lemmas.
It may  be a good idea to create new files for some lemmas as the need to be organized in a logical way.
The main lemma in this file is the correctness_gen, which should stay there.
For making this plan, check where thins were defined so it has a proper dependencies are satisfied.


Your task is to organize the lemmas in the dataplane/Timely_Infrastructure.thy file.
You will group the lemmas and definitions by similarity (e.g. they are related).
Create isabelle sections with tex description of the lemmas and definitions in the section.
Try to check the dependencies of the lemmas before moving them.

Important:
Move all lemmas at once, and use the MCP connection to check if the edit was successful.
For the lemmas break, check if it used anywhere: if is not, and if the lemma is not a simp or intro rule, them just comment it.
For those broken lemmas that are used somewhere, revert the change, put the lemma back where it was, but write a comment on top of the lemma saying: FIXME: move me to (suggestion of location)
If the move is successful you don't need to check with MCP if the source of the lemma is checking.

The file Label_Propagation_op_Correctness.thy has more than 19k lines, and it takes too long to check.
One way to improve the speed of the check is to split things into multiple files, so the checker runs in parallel for each file. And this is the main goal of waht we want: to improve the check speed of this long file.
The main lemma in this file is label_propagation_correctness (and the next ones are just consequences of it).
Everything before label_propagation_correctness must separate into new multiple files.
The hard part is to do that minding the dependencies.
So what you need to do now is to come up with a plan on how to sort and split Label_Propagation_op_Correctness.thy into multiple files.
Notice that many lemmas in Label_Propagation_op_Correctness.thy already have file that should be at.
Say some auxiliary lemma about ocaps and drop_caps could be moved to Timely_Operator_State.thy.
First learn about the files in the dataplane folder, then study Label_Propagation_op_Correctness.thy to see which new files could be
created, and which lemmas could be moved to existing files.

Later, when you start executing the plan (whenyou moving things), you need to make sure to keep things working (checking),
so you need to work in an incremental way. You will not move things before my approval of your plan, just mentioning this
so you keep that in mind for your plan.

