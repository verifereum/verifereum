Theory vfmTest2182[no_sig_docs]
Ancestors vfmTestDefs2182
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2182_0.nsv", "result2182_1.nsv", "result2182_2.nsv", "result2182_3.nsv", "result2182_4.nsv", "result2182_5.nsv", "result2182_6.nsv", "result2182_7.nsv", "result2182_8.nsv", "result2182_9.nsv", "result2182_10.nsv", "result2182_11.nsv", "result2182_12.nsv", "result2182_13.nsv", "result2182_14.nsv", "result2182_15.nsv", "result2182_16.nsv", "result2182_17.nsv", "result2182_18.nsv", "result2182_19.nsv", "result2182_20.nsv", "result2182_21.nsv", "result2182_22.nsv", "result2182_23.nsv", "result2182_24.nsv", "result2182_25.nsv", "result2182_26.nsv", "result2182_27.nsv", "result2182_28.nsv", "result2182_29.nsv", "result2182_30.nsv", "result2182_31.nsv", "result2182_32.nsv", "result2182_33.nsv", "result2182_34.nsv"];
val thyn = "vfmTestDefs2182";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
