Theory vfmTest0585[no_sig_docs]
Ancestors vfmTestDefs0585
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0585_0.nsv", "result0585_1.nsv", "result0585_2.nsv", "result0585_3.nsv", "result0585_4.nsv", "result0585_5.nsv", "result0585_6.nsv", "result0585_7.nsv", "result0585_8.nsv", "result0585_9.nsv", "result0585_10.nsv", "result0585_11.nsv", "result0585_12.nsv", "result0585_13.nsv", "result0585_14.nsv", "result0585_15.nsv", "result0585_16.nsv", "result0585_17.nsv", "result0585_18.nsv", "result0585_19.nsv", "result0585_20.nsv", "result0585_21.nsv", "result0585_22.nsv", "result0585_23.nsv", "result0585_24.nsv", "result0585_25.nsv", "result0585_26.nsv", "result0585_27.nsv", "result0585_28.nsv", "result0585_29.nsv"];
val thyn = "vfmTestDefs0585";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
