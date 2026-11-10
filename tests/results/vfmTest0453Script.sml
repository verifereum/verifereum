Theory vfmTest0453[no_sig_docs]
Ancestors vfmTestDefs0453
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0453_0.nsv", "result0453_1.nsv", "result0453_2.nsv", "result0453_3.nsv", "result0453_4.nsv", "result0453_5.nsv", "result0453_6.nsv", "result0453_7.nsv", "result0453_8.nsv", "result0453_9.nsv", "result0453_10.nsv", "result0453_11.nsv", "result0453_12.nsv", "result0453_13.nsv", "result0453_14.nsv", "result0453_15.nsv", "result0453_16.nsv", "result0453_17.nsv", "result0453_18.nsv", "result0453_19.nsv", "result0453_20.nsv", "result0453_21.nsv", "result0453_22.nsv", "result0453_23.nsv", "result0453_24.nsv", "result0453_25.nsv", "result0453_26.nsv", "result0453_27.nsv", "result0453_28.nsv", "result0453_29.nsv", "result0453_30.nsv", "result0453_31.nsv", "result0453_32.nsv", "result0453_33.nsv", "result0453_34.nsv", "result0453_35.nsv", "result0453_36.nsv", "result0453_37.nsv", "result0453_38.nsv", "result0453_39.nsv", "result0453_40.nsv", "result0453_41.nsv", "result0453_42.nsv", "result0453_43.nsv", "result0453_44.nsv", "result0453_45.nsv"];
val thyn = "vfmTestDefs0453";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
