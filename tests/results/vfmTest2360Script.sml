Theory vfmTest2360[no_sig_docs]
Ancestors vfmTestDefs2360
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2360_0.nsv", "result2360_1.nsv", "result2360_2.nsv", "result2360_3.nsv", "result2360_4.nsv", "result2360_5.nsv", "result2360_6.nsv", "result2360_7.nsv", "result2360_8.nsv", "result2360_9.nsv", "result2360_10.nsv", "result2360_11.nsv", "result2360_12.nsv", "result2360_13.nsv", "result2360_14.nsv", "result2360_15.nsv", "result2360_16.nsv", "result2360_17.nsv", "result2360_18.nsv", "result2360_19.nsv", "result2360_20.nsv", "result2360_21.nsv", "result2360_22.nsv", "result2360_23.nsv", "result2360_24.nsv", "result2360_25.nsv", "result2360_26.nsv", "result2360_27.nsv", "result2360_28.nsv", "result2360_29.nsv", "result2360_30.nsv", "result2360_31.nsv"];
val thyn = "vfmTestDefs2360";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
