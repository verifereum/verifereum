Theory vfmTest2821[no_sig_docs]
Ancestors vfmTestDefs2821
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2821_0.nsv", "result2821_1.nsv", "result2821_2.nsv"];
val thyn = "vfmTestDefs2821";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
