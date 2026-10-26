Theory vfmTest2990[no_sig_docs]
Ancestors vfmTestDefs2990
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2990_0.nsv", "result2990_1.nsv", "result2990_2.nsv", "result2990_3.nsv", "result2990_4.nsv", "result2990_5.nsv", "result2990_6.nsv", "result2990_7.nsv", "result2990_8.nsv", "result2990_9.nsv", "result2990_10.nsv", "result2990_11.nsv", "result2990_12.nsv", "result2990_13.nsv", "result2990_14.nsv", "result2990_15.nsv", "result2990_16.nsv", "result2990_17.nsv", "result2990_18.nsv", "result2990_19.nsv", "result2990_20.nsv", "result2990_21.nsv", "result2990_22.nsv", "result2990_23.nsv", "result2990_24.nsv", "result2990_25.nsv", "result2990_26.nsv", "result2990_27.nsv", "result2990_28.nsv", "result2990_29.nsv", "result2990_30.nsv", "result2990_31.nsv", "result2990_32.nsv", "result2990_33.nsv", "result2990_34.nsv", "result2990_35.nsv"];
val thyn = "vfmTestDefs2990";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
