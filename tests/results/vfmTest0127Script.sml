Theory vfmTest0127[no_sig_docs]
Ancestors vfmTestDefs0127
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0127_0.nsv", "result0127_1.nsv", "result0127_2.nsv", "result0127_3.nsv", "result0127_4.nsv", "result0127_5.nsv", "result0127_6.nsv", "result0127_7.nsv", "result0127_8.nsv", "result0127_9.nsv", "result0127_10.nsv", "result0127_11.nsv", "result0127_12.nsv", "result0127_13.nsv", "result0127_14.nsv", "result0127_15.nsv", "result0127_16.nsv", "result0127_17.nsv", "result0127_18.nsv", "result0127_19.nsv", "result0127_20.nsv", "result0127_21.nsv", "result0127_22.nsv", "result0127_23.nsv", "result0127_24.nsv", "result0127_25.nsv", "result0127_26.nsv", "result0127_27.nsv", "result0127_28.nsv", "result0127_29.nsv", "result0127_30.nsv", "result0127_31.nsv", "result0127_32.nsv", "result0127_33.nsv", "result0127_34.nsv", "result0127_35.nsv"];
val thyn = "vfmTestDefs0127";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
