Theory vfmTest0803[no_sig_docs]
Ancestors vfmTestDefs0803
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0803_0.nsv", "result0803_1.nsv", "result0803_2.nsv", "result0803_3.nsv"];
val thyn = "vfmTestDefs0803";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
