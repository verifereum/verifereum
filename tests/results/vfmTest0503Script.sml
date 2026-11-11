Theory vfmTest0503[no_sig_docs]
Ancestors vfmTestDefs0503
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0503_0.nsv", "result0503_1.nsv", "result0503_2.nsv", "result0503_3.nsv", "result0503_4.nsv", "result0503_5.nsv", "result0503_6.nsv", "result0503_7.nsv"];
val thyn = "vfmTestDefs0503";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
