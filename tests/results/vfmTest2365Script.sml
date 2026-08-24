Theory vfmTest2365[no_sig_docs]
Ancestors vfmTestDefs2365
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2365_0.nsv", "result2365_1.nsv", "result2365_2.nsv", "result2365_3.nsv", "result2365_4.nsv"];
val thyn = "vfmTestDefs2365";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
