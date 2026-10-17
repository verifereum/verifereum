Theory vfmTest2086[no_sig_docs]
Ancestors vfmTestDefs2086
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2086_0.nsv", "result2086_1.nsv", "result2086_2.nsv", "result2086_3.nsv", "result2086_4.nsv", "result2086_5.nsv", "result2086_6.nsv", "result2086_7.nsv", "result2086_8.nsv", "result2086_9.nsv", "result2086_10.nsv", "result2086_11.nsv", "result2086_12.nsv", "result2086_13.nsv", "result2086_14.nsv", "result2086_15.nsv", "result2086_16.nsv", "result2086_17.nsv", "result2086_18.nsv", "result2086_19.nsv", "result2086_20.nsv", "result2086_21.nsv", "result2086_22.nsv", "result2086_23.nsv", "result2086_24.nsv", "result2086_25.nsv", "result2086_26.nsv", "result2086_27.nsv", "result2086_28.nsv", "result2086_29.nsv"];
val thyn = "vfmTestDefs2086";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
