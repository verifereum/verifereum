Theory vfmTest0699[no_sig_docs]
Ancestors vfmTestDefs0699
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0699_0.nsv", "result0699_1.nsv", "result0699_2.nsv", "result0699_3.nsv", "result0699_4.nsv", "result0699_5.nsv", "result0699_6.nsv", "result0699_7.nsv", "result0699_8.nsv", "result0699_9.nsv", "result0699_10.nsv", "result0699_11.nsv", "result0699_12.nsv", "result0699_13.nsv", "result0699_14.nsv", "result0699_15.nsv"];
val thyn = "vfmTestDefs0699";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
