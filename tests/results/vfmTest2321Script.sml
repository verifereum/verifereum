Theory vfmTest2321[no_sig_docs]
Ancestors vfmTestDefs2321
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2321_0.nsv", "result2321_1.nsv"];
val thyn = "vfmTestDefs2321";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
