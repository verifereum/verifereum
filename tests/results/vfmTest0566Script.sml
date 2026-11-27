Theory vfmTest0566[no_sig_docs]
Ancestors vfmTestDefs0566
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0566_0.nsv", "result0566_1.nsv", "result0566_2.nsv", "result0566_3.nsv", "result0566_4.nsv", "result0566_5.nsv", "result0566_6.nsv", "result0566_7.nsv", "result0566_8.nsv", "result0566_9.nsv", "result0566_10.nsv", "result0566_11.nsv", "result0566_12.nsv", "result0566_13.nsv", "result0566_14.nsv", "result0566_15.nsv", "result0566_16.nsv", "result0566_17.nsv", "result0566_18.nsv", "result0566_19.nsv", "result0566_20.nsv", "result0566_21.nsv", "result0566_22.nsv", "result0566_23.nsv"];
val thyn = "vfmTestDefs0566";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
