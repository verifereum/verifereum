Theory vfmTest2613[no_sig_docs]
Ancestors vfmTestDefs2613
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2613_0.nsv", "result2613_1.nsv", "result2613_2.nsv", "result2613_3.nsv"];
val thyn = "vfmTestDefs2613";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
