Theory vfmTest2256[no_sig_docs]
Ancestors vfmTestDefs2256
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2256_0.nsv", "result2256_1.nsv", "result2256_2.nsv", "result2256_3.nsv", "result2256_4.nsv", "result2256_5.nsv", "result2256_6.nsv", "result2256_7.nsv", "result2256_8.nsv", "result2256_9.nsv", "result2256_10.nsv", "result2256_11.nsv", "result2256_12.nsv", "result2256_13.nsv", "result2256_14.nsv", "result2256_15.nsv", "result2256_16.nsv", "result2256_17.nsv", "result2256_18.nsv", "result2256_19.nsv", "result2256_20.nsv", "result2256_21.nsv", "result2256_22.nsv", "result2256_23.nsv", "result2256_24.nsv", "result2256_25.nsv", "result2256_26.nsv"];
val thyn = "vfmTestDefs2256";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
