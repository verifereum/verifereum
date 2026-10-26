Theory vfmTest0921[no_sig_docs]
Ancestors vfmTestDefs0921
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0921_0.nsv", "result0921_1.nsv", "result0921_2.nsv", "result0921_3.nsv", "result0921_4.nsv", "result0921_5.nsv", "result0921_6.nsv", "result0921_7.nsv", "result0921_8.nsv", "result0921_9.nsv"];
val thyn = "vfmTestDefs0921";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
