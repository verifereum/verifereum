Theory vfmTest2446[no_sig_docs]
Ancestors vfmTestDefs2446
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2446_0.nsv", "result2446_1.nsv", "result2446_2.nsv", "result2446_3.nsv", "result2446_4.nsv", "result2446_5.nsv", "result2446_6.nsv", "result2446_7.nsv", "result2446_8.nsv", "result2446_9.nsv", "result2446_10.nsv", "result2446_11.nsv", "result2446_12.nsv", "result2446_13.nsv", "result2446_14.nsv", "result2446_15.nsv", "result2446_16.nsv", "result2446_17.nsv", "result2446_18.nsv", "result2446_19.nsv", "result2446_20.nsv", "result2446_21.nsv", "result2446_22.nsv", "result2446_23.nsv", "result2446_24.nsv", "result2446_25.nsv", "result2446_26.nsv", "result2446_27.nsv", "result2446_28.nsv", "result2446_29.nsv"];
val thyn = "vfmTestDefs2446";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
