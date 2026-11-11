Theory vfmTest2214[no_sig_docs]
Ancestors vfmTestDefs2214
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2214_0.nsv", "result2214_1.nsv", "result2214_2.nsv", "result2214_3.nsv", "result2214_4.nsv", "result2214_5.nsv", "result2214_6.nsv", "result2214_7.nsv", "result2214_8.nsv", "result2214_9.nsv", "result2214_10.nsv", "result2214_11.nsv", "result2214_12.nsv", "result2214_13.nsv", "result2214_14.nsv", "result2214_15.nsv", "result2214_16.nsv", "result2214_17.nsv", "result2214_18.nsv", "result2214_19.nsv", "result2214_20.nsv", "result2214_21.nsv", "result2214_22.nsv", "result2214_23.nsv", "result2214_24.nsv", "result2214_25.nsv", "result2214_26.nsv", "result2214_27.nsv", "result2214_28.nsv", "result2214_29.nsv", "result2214_30.nsv", "result2214_31.nsv", "result2214_32.nsv", "result2214_33.nsv", "result2214_34.nsv", "result2214_35.nsv", "result2214_36.nsv", "result2214_37.nsv", "result2214_38.nsv", "result2214_39.nsv", "result2214_40.nsv", "result2214_41.nsv", "result2214_42.nsv", "result2214_43.nsv", "result2214_44.nsv", "result2214_45.nsv", "result2214_46.nsv", "result2214_47.nsv"];
val thyn = "vfmTestDefs2214";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
