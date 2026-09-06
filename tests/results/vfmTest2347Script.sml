Theory vfmTest2347[no_sig_docs]
Ancestors vfmTestDefs2347
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2347_0.nsv", "result2347_1.nsv", "result2347_2.nsv", "result2347_3.nsv", "result2347_4.nsv", "result2347_5.nsv", "result2347_6.nsv", "result2347_7.nsv", "result2347_8.nsv", "result2347_9.nsv", "result2347_10.nsv", "result2347_11.nsv", "result2347_12.nsv", "result2347_13.nsv", "result2347_14.nsv", "result2347_15.nsv", "result2347_16.nsv", "result2347_17.nsv", "result2347_18.nsv", "result2347_19.nsv", "result2347_20.nsv", "result2347_21.nsv", "result2347_22.nsv", "result2347_23.nsv", "result2347_24.nsv", "result2347_25.nsv", "result2347_26.nsv", "result2347_27.nsv", "result2347_28.nsv", "result2347_29.nsv", "result2347_30.nsv", "result2347_31.nsv", "result2347_32.nsv", "result2347_33.nsv", "result2347_34.nsv", "result2347_35.nsv"];
val thyn = "vfmTestDefs2347";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
