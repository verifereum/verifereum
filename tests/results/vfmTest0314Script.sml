Theory vfmTest0314[no_sig_docs]
Ancestors vfmTestDefs0314
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0314_0.nsv", "result0314_1.nsv", "result0314_2.nsv", "result0314_3.nsv", "result0314_4.nsv", "result0314_5.nsv", "result0314_6.nsv", "result0314_7.nsv", "result0314_8.nsv", "result0314_9.nsv", "result0314_10.nsv", "result0314_11.nsv", "result0314_12.nsv", "result0314_13.nsv", "result0314_14.nsv", "result0314_15.nsv"];
val thyn = "vfmTestDefs0314";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
