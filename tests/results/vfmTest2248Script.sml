Theory vfmTest2248[no_sig_docs]
Ancestors vfmTestDefs2248
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2248_0.nsv", "result2248_1.nsv", "result2248_2.nsv", "result2248_3.nsv", "result2248_4.nsv", "result2248_5.nsv", "result2248_6.nsv", "result2248_7.nsv", "result2248_8.nsv", "result2248_9.nsv", "result2248_10.nsv", "result2248_11.nsv", "result2248_12.nsv", "result2248_13.nsv", "result2248_14.nsv", "result2248_15.nsv", "result2248_16.nsv", "result2248_17.nsv", "result2248_18.nsv", "result2248_19.nsv", "result2248_20.nsv", "result2248_21.nsv", "result2248_22.nsv", "result2248_23.nsv", "result2248_24.nsv", "result2248_25.nsv", "result2248_26.nsv", "result2248_27.nsv", "result2248_28.nsv", "result2248_29.nsv", "result2248_30.nsv", "result2248_31.nsv", "result2248_32.nsv", "result2248_33.nsv", "result2248_34.nsv", "result2248_35.nsv", "result2248_36.nsv", "result2248_37.nsv", "result2248_38.nsv", "result2248_39.nsv", "result2248_40.nsv", "result2248_41.nsv", "result2248_42.nsv", "result2248_43.nsv", "result2248_44.nsv", "result2248_45.nsv", "result2248_46.nsv"];
val thyn = "vfmTestDefs2248";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
