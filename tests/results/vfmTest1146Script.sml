Theory vfmTest1146[no_sig_docs]
Ancestors vfmTestDefs1146
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1146_0.nsv", "result1146_1.nsv"];
val thyn = "vfmTestDefs1146";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
