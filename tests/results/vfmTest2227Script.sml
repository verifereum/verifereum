Theory vfmTest2227[no_sig_docs]
Ancestors vfmTestDefs2227
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2227_0.nsv", "result2227_1.nsv", "result2227_2.nsv", "result2227_3.nsv", "result2227_4.nsv", "result2227_5.nsv", "result2227_6.nsv", "result2227_7.nsv", "result2227_8.nsv", "result2227_9.nsv", "result2227_10.nsv", "result2227_11.nsv", "result2227_12.nsv", "result2227_13.nsv", "result2227_14.nsv", "result2227_15.nsv", "result2227_16.nsv", "result2227_17.nsv", "result2227_18.nsv", "result2227_19.nsv"];
val thyn = "vfmTestDefs2227";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
