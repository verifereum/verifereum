Theory vfmTest0613[no_sig_docs]
Ancestors vfmTestDefs0613
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0613_0.nsv", "result0613_1.nsv", "result0613_2.nsv", "result0613_3.nsv", "result0613_4.nsv", "result0613_5.nsv", "result0613_6.nsv", "result0613_7.nsv", "result0613_8.nsv", "result0613_9.nsv", "result0613_10.nsv", "result0613_11.nsv", "result0613_12.nsv", "result0613_13.nsv", "result0613_14.nsv", "result0613_15.nsv", "result0613_16.nsv", "result0613_17.nsv", "result0613_18.nsv", "result0613_19.nsv", "result0613_20.nsv", "result0613_21.nsv", "result0613_22.nsv", "result0613_23.nsv"];
val thyn = "vfmTestDefs0613";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
