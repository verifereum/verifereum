Theory vfmTest2183[no_sig_docs]
Ancestors vfmTestDefs2183
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2183_0.nsv", "result2183_1.nsv", "result2183_2.nsv", "result2183_3.nsv"];
val thyn = "vfmTestDefs2183";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
