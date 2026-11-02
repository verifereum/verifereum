Theory vfmTest0414[no_sig_docs]
Ancestors vfmTestDefs0414
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0414_0.nsv", "result0414_1.nsv", "result0414_2.nsv", "result0414_3.nsv", "result0414_4.nsv", "result0414_5.nsv", "result0414_6.nsv", "result0414_7.nsv"];
val thyn = "vfmTestDefs0414";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
