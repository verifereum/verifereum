Theory vfmTest2352[no_sig_docs]
Ancestors vfmTestDefs2352
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2352_0.nsv", "result2352_1.nsv", "result2352_2.nsv", "result2352_3.nsv", "result2352_4.nsv", "result2352_5.nsv", "result2352_6.nsv", "result2352_7.nsv", "result2352_8.nsv", "result2352_9.nsv", "result2352_10.nsv", "result2352_11.nsv", "result2352_12.nsv", "result2352_13.nsv", "result2352_14.nsv", "result2352_15.nsv", "result2352_16.nsv", "result2352_17.nsv", "result2352_18.nsv", "result2352_19.nsv"];
val thyn = "vfmTestDefs2352";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
