Theory vfmTest2715[no_sig_docs]
Ancestors vfmTestDefs2715
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2715_0.nsv", "result2715_1.nsv", "result2715_2.nsv", "result2715_3.nsv", "result2715_4.nsv", "result2715_5.nsv", "result2715_6.nsv", "result2715_7.nsv", "result2715_8.nsv", "result2715_9.nsv", "result2715_10.nsv", "result2715_11.nsv", "result2715_12.nsv", "result2715_13.nsv", "result2715_14.nsv", "result2715_15.nsv", "result2715_16.nsv", "result2715_17.nsv", "result2715_18.nsv", "result2715_19.nsv", "result2715_20.nsv", "result2715_21.nsv", "result2715_22.nsv", "result2715_23.nsv", "result2715_24.nsv", "result2715_25.nsv", "result2715_26.nsv", "result2715_27.nsv", "result2715_28.nsv", "result2715_29.nsv", "result2715_30.nsv", "result2715_31.nsv", "result2715_32.nsv", "result2715_33.nsv", "result2715_34.nsv", "result2715_35.nsv", "result2715_36.nsv", "result2715_37.nsv", "result2715_38.nsv", "result2715_39.nsv"];
val thyn = "vfmTestDefs2715";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
