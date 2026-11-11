Theory vfmTest0030[no_sig_docs]
Ancestors vfmTestDefs0030
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0030_0.nsv", "result0030_1.nsv", "result0030_2.nsv", "result0030_3.nsv", "result0030_4.nsv", "result0030_5.nsv", "result0030_6.nsv", "result0030_7.nsv", "result0030_8.nsv", "result0030_9.nsv", "result0030_10.nsv", "result0030_11.nsv", "result0030_12.nsv", "result0030_13.nsv", "result0030_14.nsv", "result0030_15.nsv", "result0030_16.nsv", "result0030_17.nsv", "result0030_18.nsv", "result0030_19.nsv", "result0030_20.nsv", "result0030_21.nsv", "result0030_22.nsv", "result0030_23.nsv", "result0030_24.nsv", "result0030_25.nsv", "result0030_26.nsv", "result0030_27.nsv", "result0030_28.nsv", "result0030_29.nsv", "result0030_30.nsv", "result0030_31.nsv", "result0030_32.nsv", "result0030_33.nsv", "result0030_34.nsv", "result0030_35.nsv", "result0030_36.nsv", "result0030_37.nsv", "result0030_38.nsv", "result0030_39.nsv", "result0030_40.nsv", "result0030_41.nsv", "result0030_42.nsv", "result0030_43.nsv", "result0030_44.nsv", "result0030_45.nsv", "result0030_46.nsv"];
val thyn = "vfmTestDefs0030";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
