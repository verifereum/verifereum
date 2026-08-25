Theory vfmTest2266[no_sig_docs]
Ancestors vfmTestDefs2266
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2266_0.nsv", "result2266_1.nsv"];
val thyn = "vfmTestDefs2266";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
