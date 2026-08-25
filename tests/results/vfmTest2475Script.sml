Theory vfmTest2475[no_sig_docs]
Ancestors vfmTestDefs2475
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2475_0.nsv", "result2475_1.nsv", "result2475_2.nsv", "result2475_3.nsv", "result2475_4.nsv", "result2475_5.nsv", "result2475_6.nsv", "result2475_7.nsv", "result2475_8.nsv", "result2475_9.nsv", "result2475_10.nsv", "result2475_11.nsv", "result2475_12.nsv", "result2475_13.nsv", "result2475_14.nsv", "result2475_15.nsv", "result2475_16.nsv", "result2475_17.nsv", "result2475_18.nsv", "result2475_19.nsv", "result2475_20.nsv", "result2475_21.nsv", "result2475_22.nsv", "result2475_23.nsv", "result2475_24.nsv", "result2475_25.nsv", "result2475_26.nsv", "result2475_27.nsv", "result2475_28.nsv", "result2475_29.nsv"];
val thyn = "vfmTestDefs2475";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
