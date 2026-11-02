Theory vfmTest2486[no_sig_docs]
Ancestors vfmTestDefs2486
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2486_0.nsv", "result2486_1.nsv", "result2486_2.nsv", "result2486_3.nsv", "result2486_4.nsv", "result2486_5.nsv", "result2486_6.nsv", "result2486_7.nsv", "result2486_8.nsv", "result2486_9.nsv", "result2486_10.nsv", "result2486_11.nsv", "result2486_12.nsv", "result2486_13.nsv", "result2486_14.nsv", "result2486_15.nsv", "result2486_16.nsv", "result2486_17.nsv", "result2486_18.nsv", "result2486_19.nsv", "result2486_20.nsv", "result2486_21.nsv", "result2486_22.nsv", "result2486_23.nsv", "result2486_24.nsv", "result2486_25.nsv", "result2486_26.nsv", "result2486_27.nsv", "result2486_28.nsv", "result2486_29.nsv", "result2486_30.nsv", "result2486_31.nsv"];
val thyn = "vfmTestDefs2486";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
