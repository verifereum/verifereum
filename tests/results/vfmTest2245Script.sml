Theory vfmTest2245[no_sig_docs]
Ancestors vfmTestDefs2245
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2245_0.nsv", "result2245_1.nsv", "result2245_2.nsv", "result2245_3.nsv"];
val thyn = "vfmTestDefs2245";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
