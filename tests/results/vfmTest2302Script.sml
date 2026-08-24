Theory vfmTest2302[no_sig_docs]
Ancestors vfmTestDefs2302
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2302_0.nsv", "result2302_1.nsv"];
val thyn = "vfmTestDefs2302";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
