Theory vfmTest0295[no_sig_docs]
Ancestors vfmTestDefs0295
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0295_0.nsv", "result0295_1.nsv", "result0295_2.nsv", "result0295_3.nsv", "result0295_4.nsv", "result0295_5.nsv"];
val thyn = "vfmTestDefs0295";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
