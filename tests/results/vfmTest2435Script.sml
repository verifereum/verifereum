Theory vfmTest2435[no_sig_docs]
Ancestors vfmTestDefs2435
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2435_0.nsv", "result2435_1.nsv", "result2435_2.nsv"];
val thyn = "vfmTestDefs2435";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
