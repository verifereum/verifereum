Theory vfmTest2896[no_sig_docs]
Ancestors vfmTestDefs2896
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2896_0.nsv"];
val thyn = "vfmTestDefs2896";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
