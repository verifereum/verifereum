Theory vfmTest0791[no_sig_docs]
Ancestors vfmTestDefs0791
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0791_0.nsv", "result0791_1.nsv", "result0791_2.nsv", "result0791_3.nsv", "result0791_4.nsv", "result0791_5.nsv", "result0791_6.nsv", "result0791_7.nsv"];
val thyn = "vfmTestDefs0791";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
