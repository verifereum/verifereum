Theory vfmTest0718[no_sig_docs]
Ancestors vfmTestDefs0718
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0718_0.nsv", "result0718_1.nsv", "result0718_2.nsv", "result0718_3.nsv", "result0718_4.nsv", "result0718_5.nsv", "result0718_6.nsv", "result0718_7.nsv", "result0718_8.nsv", "result0718_9.nsv", "result0718_10.nsv", "result0718_11.nsv", "result0718_12.nsv", "result0718_13.nsv", "result0718_14.nsv", "result0718_15.nsv", "result0718_16.nsv", "result0718_17.nsv", "result0718_18.nsv", "result0718_19.nsv", "result0718_20.nsv", "result0718_21.nsv", "result0718_22.nsv", "result0718_23.nsv", "result0718_24.nsv", "result0718_25.nsv", "result0718_26.nsv", "result0718_27.nsv", "result0718_28.nsv", "result0718_29.nsv", "result0718_30.nsv", "result0718_31.nsv", "result0718_32.nsv", "result0718_33.nsv", "result0718_34.nsv", "result0718_35.nsv", "result0718_36.nsv", "result0718_37.nsv"];
val thyn = "vfmTestDefs0718";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
