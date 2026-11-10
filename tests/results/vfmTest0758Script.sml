Theory vfmTest0758[no_sig_docs]
Ancestors vfmTestDefs0758
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0758_0.nsv", "result0758_1.nsv", "result0758_2.nsv", "result0758_3.nsv"];
val thyn = "vfmTestDefs0758";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
