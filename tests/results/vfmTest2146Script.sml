Theory vfmTest2146[no_sig_docs]
Ancestors vfmTestDefs2146
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2146_0.nsv"];
val thyn = "vfmTestDefs2146";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
