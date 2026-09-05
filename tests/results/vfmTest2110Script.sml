Theory vfmTest2110[no_sig_docs]
Ancestors vfmTestDefs2110
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2110_0.nsv", "result2110_1.nsv", "result2110_2.nsv", "result2110_3.nsv", "result2110_4.nsv", "result2110_5.nsv", "result2110_6.nsv", "result2110_7.nsv", "result2110_8.nsv", "result2110_9.nsv", "result2110_10.nsv", "result2110_11.nsv", "result2110_12.nsv", "result2110_13.nsv", "result2110_14.nsv", "result2110_15.nsv", "result2110_16.nsv", "result2110_17.nsv", "result2110_18.nsv", "result2110_19.nsv", "result2110_20.nsv", "result2110_21.nsv", "result2110_22.nsv", "result2110_23.nsv", "result2110_24.nsv", "result2110_25.nsv", "result2110_26.nsv", "result2110_27.nsv", "result2110_28.nsv", "result2110_29.nsv"];
val thyn = "vfmTestDefs2110";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
