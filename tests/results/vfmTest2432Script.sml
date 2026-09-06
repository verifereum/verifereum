Theory vfmTest2432[no_sig_docs]
Ancestors vfmTestDefs2432
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2432_0.nsv", "result2432_1.nsv", "result2432_2.nsv", "result2432_3.nsv", "result2432_4.nsv", "result2432_5.nsv", "result2432_6.nsv", "result2432_7.nsv", "result2432_8.nsv", "result2432_9.nsv", "result2432_10.nsv", "result2432_11.nsv", "result2432_12.nsv", "result2432_13.nsv", "result2432_14.nsv", "result2432_15.nsv", "result2432_16.nsv", "result2432_17.nsv", "result2432_18.nsv", "result2432_19.nsv", "result2432_20.nsv", "result2432_21.nsv", "result2432_22.nsv", "result2432_23.nsv", "result2432_24.nsv", "result2432_25.nsv", "result2432_26.nsv", "result2432_27.nsv", "result2432_28.nsv", "result2432_29.nsv", "result2432_30.nsv", "result2432_31.nsv", "result2432_32.nsv", "result2432_33.nsv", "result2432_34.nsv", "result2432_35.nsv", "result2432_36.nsv", "result2432_37.nsv", "result2432_38.nsv", "result2432_39.nsv"];
val thyn = "vfmTestDefs2432";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
