Theory vfmTest0400[no_sig_docs]
Ancestors vfmTestDefs0400
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0400_0.nsv", "result0400_1.nsv", "result0400_2.nsv", "result0400_3.nsv", "result0400_4.nsv", "result0400_5.nsv", "result0400_6.nsv", "result0400_7.nsv", "result0400_8.nsv", "result0400_9.nsv", "result0400_10.nsv", "result0400_11.nsv", "result0400_12.nsv", "result0400_13.nsv", "result0400_14.nsv", "result0400_15.nsv", "result0400_16.nsv", "result0400_17.nsv", "result0400_18.nsv", "result0400_19.nsv", "result0400_20.nsv", "result0400_21.nsv", "result0400_22.nsv", "result0400_23.nsv", "result0400_24.nsv", "result0400_25.nsv", "result0400_26.nsv", "result0400_27.nsv", "result0400_28.nsv", "result0400_29.nsv", "result0400_30.nsv", "result0400_31.nsv", "result0400_32.nsv", "result0400_33.nsv", "result0400_34.nsv", "result0400_35.nsv"];
val thyn = "vfmTestDefs0400";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
