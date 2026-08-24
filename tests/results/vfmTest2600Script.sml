Theory vfmTest2600[no_sig_docs]
Ancestors vfmTestDefs2600
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2600_0.nsv", "result2600_1.nsv", "result2600_2.nsv", "result2600_3.nsv"];
val thyn = "vfmTestDefs2600";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
