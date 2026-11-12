Theory vfmTest2267[no_sig_docs]
Ancestors vfmTestDefs2267
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2267_0.nsv", "result2267_1.nsv", "result2267_2.nsv", "result2267_3.nsv", "result2267_4.nsv", "result2267_5.nsv", "result2267_6.nsv", "result2267_7.nsv", "result2267_8.nsv", "result2267_9.nsv", "result2267_10.nsv", "result2267_11.nsv", "result2267_12.nsv", "result2267_13.nsv", "result2267_14.nsv", "result2267_15.nsv"];
val thyn = "vfmTestDefs2267";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
