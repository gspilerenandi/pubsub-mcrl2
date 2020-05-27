# ABOUT THE MODELS
There are two models in the v4 folder, mv4 and mv4small:

  * mv4.mcrl2: the most complete of the two. It contains two subscribers (s1 and s2), two publishers
         (p1 and p2), two topics (top1 and top2), a broker (locbrk), and a single event to (ev).

  * mv4small.mcrl2: this one is a reduced version of the mv4 model. It contains one subscriber (s1),
              one publisher (p1), the broker (locbrk), one topic (top2), and one event (ev2).


# TOOLS INSTRUCTIONS
After moving to the v4 folder directory, you can perform the following actions depending on what
you need to do. Substitute <M> for either mv4 or mv4small bellow depending on which one you
intend to use. I've used *, **, and *** to progressively identify the operations that can take
the longest to be completed.

  1 - transforming a mcrl2 model to a linear process specification (used for the step by step
      simulation)

                              mcrl22lps -v <M>.mcrl2 <M>.lps

  2*** - transforming a linear process specification to a labelled transition system (used
      for the graph representation).

                              lps2lts -v <M>.lps <M>.lts

  3* - using the generated lts to apply a property previously defined on a .mcf file.

                              lts2pbes -c <M>.lts -f mv4p.mcf <M>.pbes

  4** - checking the model against the defined property and generating a counter examples
      that will be stored on the <M>_evi.lts

            pbessolve --evidence-file=<M>_evi.lts --file=<M>.lts --in=pbes --verbose <M>.pbes


# mCRL2: FILES AND TOOLS
In this section I just want to give a quick overview of the what are the files in the v4 folder
and how to use the correct mCRL2 tools for each file.

  FILES:
      mv4p.mcf: contains properties to be validated

  TOOLS:
      lpsxsim: runs a textual simulation of the functioning of the system. The user can navigate
               through the system's states by performing actions. Takes .lps files as input.

      ltsgraph: displays a graph representation of the system. Can also be used to display a
                counter example (<M>_evi.lts). Takes .lts files as input.
