Theory vfmTest2151[no_sig_docs]
Ancestors vfmTestDefs2151
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2151_0.nsv", "result2151_1.nsv", "result2151_2.nsv", "result2151_3.nsv", "result2151_4.nsv", "result2151_5.nsv", "result2151_6.nsv", "result2151_7.nsv", "result2151_8.nsv", "result2151_9.nsv", "result2151_10.nsv", "result2151_11.nsv", "result2151_12.nsv", "result2151_13.nsv", "result2151_14.nsv", "result2151_15.nsv", "result2151_16.nsv", "result2151_17.nsv", "result2151_18.nsv", "result2151_19.nsv", "result2151_20.nsv", "result2151_21.nsv", "result2151_22.nsv", "result2151_23.nsv", "result2151_24.nsv", "result2151_25.nsv", "result2151_26.nsv"];
val thyn = "vfmTestDefs2151";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
