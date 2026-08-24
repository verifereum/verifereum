Theory vfmTest0091[no_sig_docs]
Ancestors vfmTestDefs0091
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0091_0.nsv", "result0091_1.nsv", "result0091_2.nsv", "result0091_3.nsv", "result0091_4.nsv", "result0091_5.nsv", "result0091_6.nsv", "result0091_7.nsv", "result0091_8.nsv", "result0091_9.nsv", "result0091_10.nsv", "result0091_11.nsv", "result0091_12.nsv", "result0091_13.nsv", "result0091_14.nsv", "result0091_15.nsv", "result0091_16.nsv", "result0091_17.nsv", "result0091_18.nsv", "result0091_19.nsv", "result0091_20.nsv", "result0091_21.nsv", "result0091_22.nsv", "result0091_23.nsv", "result0091_24.nsv", "result0091_25.nsv", "result0091_26.nsv", "result0091_27.nsv", "result0091_28.nsv", "result0091_29.nsv", "result0091_30.nsv", "result0091_31.nsv", "result0091_32.nsv", "result0091_33.nsv", "result0091_34.nsv", "result0091_35.nsv", "result0091_36.nsv", "result0091_37.nsv", "result0091_38.nsv", "result0091_39.nsv"];
val thyn = "vfmTestDefs0091";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
