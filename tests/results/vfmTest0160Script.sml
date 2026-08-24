Theory vfmTest0160[no_sig_docs]
Ancestors vfmTestDefs0160
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0160_0.nsv", "result0160_1.nsv", "result0160_2.nsv", "result0160_3.nsv", "result0160_4.nsv", "result0160_5.nsv", "result0160_6.nsv", "result0160_7.nsv", "result0160_8.nsv", "result0160_9.nsv", "result0160_10.nsv", "result0160_11.nsv", "result0160_12.nsv", "result0160_13.nsv", "result0160_14.nsv", "result0160_15.nsv", "result0160_16.nsv", "result0160_17.nsv", "result0160_18.nsv", "result0160_19.nsv", "result0160_20.nsv", "result0160_21.nsv", "result0160_22.nsv", "result0160_23.nsv", "result0160_24.nsv", "result0160_25.nsv", "result0160_26.nsv", "result0160_27.nsv", "result0160_28.nsv", "result0160_29.nsv", "result0160_30.nsv", "result0160_31.nsv", "result0160_32.nsv", "result0160_33.nsv", "result0160_34.nsv", "result0160_35.nsv", "result0160_36.nsv", "result0160_37.nsv", "result0160_38.nsv", "result0160_39.nsv"];
val thyn = "vfmTestDefs0160";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
