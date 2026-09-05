Theory vfmTest0075[no_sig_docs]
Ancestors vfmTestDefs0075
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0075_0.nsv", "result0075_1.nsv", "result0075_2.nsv", "result0075_3.nsv"];
val thyn = "vfmTestDefs0075";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
