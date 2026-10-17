Theory vfmTest2249[no_sig_docs]
Ancestors vfmTestDefs2249
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2249_0.nsv", "result2249_1.nsv", "result2249_2.nsv", "result2249_3.nsv", "result2249_4.nsv", "result2249_5.nsv", "result2249_6.nsv", "result2249_7.nsv", "result2249_8.nsv", "result2249_9.nsv", "result2249_10.nsv", "result2249_11.nsv", "result2249_12.nsv", "result2249_13.nsv", "result2249_14.nsv", "result2249_15.nsv", "result2249_16.nsv", "result2249_17.nsv", "result2249_18.nsv", "result2249_19.nsv", "result2249_20.nsv", "result2249_21.nsv", "result2249_22.nsv", "result2249_23.nsv", "result2249_24.nsv", "result2249_25.nsv", "result2249_26.nsv", "result2249_27.nsv", "result2249_28.nsv", "result2249_29.nsv", "result2249_30.nsv", "result2249_31.nsv", "result2249_32.nsv", "result2249_33.nsv", "result2249_34.nsv", "result2249_35.nsv"];
val thyn = "vfmTestDefs2249";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
