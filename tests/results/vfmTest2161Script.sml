Theory vfmTest2161[no_sig_docs]
Ancestors vfmTestDefs2161
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2161_0.nsv", "result2161_1.nsv", "result2161_2.nsv", "result2161_3.nsv", "result2161_4.nsv", "result2161_5.nsv", "result2161_6.nsv", "result2161_7.nsv", "result2161_8.nsv", "result2161_9.nsv", "result2161_10.nsv", "result2161_11.nsv", "result2161_12.nsv", "result2161_13.nsv", "result2161_14.nsv", "result2161_15.nsv", "result2161_16.nsv", "result2161_17.nsv", "result2161_18.nsv", "result2161_19.nsv", "result2161_20.nsv", "result2161_21.nsv", "result2161_22.nsv", "result2161_23.nsv", "result2161_24.nsv", "result2161_25.nsv", "result2161_26.nsv"];
val thyn = "vfmTestDefs2161";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
