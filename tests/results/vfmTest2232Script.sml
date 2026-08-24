Theory vfmTest2232[no_sig_docs]
Ancestors vfmTestDefs2232
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2232_0.nsv", "result2232_1.nsv"];
val thyn = "vfmTestDefs2232";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
