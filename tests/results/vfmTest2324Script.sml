Theory vfmTest2324[no_sig_docs]
Ancestors vfmTestDefs2324
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2324_0.nsv", "result2324_1.nsv", "result2324_2.nsv", "result2324_3.nsv", "result2324_4.nsv", "result2324_5.nsv", "result2324_6.nsv", "result2324_7.nsv", "result2324_8.nsv", "result2324_9.nsv", "result2324_10.nsv", "result2324_11.nsv", "result2324_12.nsv", "result2324_13.nsv", "result2324_14.nsv", "result2324_15.nsv", "result2324_16.nsv", "result2324_17.nsv", "result2324_18.nsv", "result2324_19.nsv", "result2324_20.nsv", "result2324_21.nsv", "result2324_22.nsv", "result2324_23.nsv", "result2324_24.nsv", "result2324_25.nsv", "result2324_26.nsv", "result2324_27.nsv", "result2324_28.nsv", "result2324_29.nsv", "result2324_30.nsv", "result2324_31.nsv", "result2324_32.nsv", "result2324_33.nsv", "result2324_34.nsv", "result2324_35.nsv"];
val thyn = "vfmTestDefs2324";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
