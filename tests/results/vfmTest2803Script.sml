Theory vfmTest2803[no_sig_docs]
Ancestors vfmTestDefs2803
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2803_0.nsv", "result2803_1.nsv", "result2803_2.nsv", "result2803_3.nsv"];
val thyn = "vfmTestDefs2803";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
