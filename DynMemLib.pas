{
    Copyright (C) 2024

    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"),
    to deal in the Software without restriction, including without limitation
    the rights to use, copy, modify, merge, publish, distribute, sublicense,
    and/or sell copies of the Software, and to permit persons to whom the
    Software is furnished to do so, subject to the following conditions:
    The above copyright notice and this permission notice shall be included
    in all copies or substantial portions of the Software.
    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
    EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
    MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
    IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
    DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
    TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE
    OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

    See MSDN docs for some of the following constants and structures:
    Also, see https://microsoft.github.io/windows-docs-rs/doc/windows...

    Reference implementation: BTMemoryModule.
    Additional disclaimer: The code in (this) DynMemLib.pas file has been entirely written from scratch,
    following BTMemoryModule as a reference implementation. No code has been copied, including constants and type definitions.
    It follows much of its logic, structure and approaches.
}


unit DynMemLib;

{$mode Delphi}{$H+}
{$WARN 4056 off : Conversion between ordinals and pointers is not portable}
interface

uses
  Windows, Classes;


type
  TMemLibSection = record
    Address: Pointer;
    Size: DWord;
  end;

  TMemLibSectionArray = array of TMemLibSection;

  TDynMemLib = class
  private
    FSections: TMemLibSectionArray;
    FInitialized: Boolean;
    FLibHeaders: PImageNtHeaders;
    FCodeAddr: Pointer;
    FImportedLibsAddr: Pointer;
    FImportedLibsCount: Integer;
    FProtectDiscardableSection: Boolean;
    FProtectNonDiscardableSection: Boolean;
    FAttachLibraryOnLoad: Boolean;

    procedure SetTableSections(ALibData: Pointer; AOldHeaders: TImageNtHeaders);
    procedure RelocateImageBase(AAmount: UInt64);
    procedure LoadImports;
    procedure ProtectTableSections;
  public
    constructor Create;
    destructor Destroy; override;
    procedure SetProtectionFlags(AProtectDiscardableSection, AProtectNonDiscardableSection: Boolean);
    function MemLoadLibrary(ALibData: Pointer): Boolean; overload;
    function MemGetProcAddress(AFuncName: PChar): Pointer; overload;
    function MemGetProcAddress(AFuncName: string): Pointer; overload;
    procedure MemFreeLibrary;

    //This option has to be set/reset before calling MemLoadLibrary, to decide if the library's entry point can be called. By default, it is True.
    property AttachLibraryOnLoad: Boolean read FAttachLibraryOnLoad write FAttachLibraryOnLoad;
  end;


implementation

uses
  SysUtils;

const
  IMAGE_SIZEOF_BASE_RELOCATION: DWord = 8;
  IMAGE_REL_BASED_HIGHLOW: DWord = 3; //from PE Format

  {$IFNDEF FPC}
    IMAGE_ORDINAL_FLAG32: DWord = $80000000;  //not defined in (old versions of) Delphi
    IMAGE_ORDINAL_FLAG64: UInt64 = UInt64($8000000000000000);  //not defined in (old versions of) Delphi
  {$ENDIF}

type
  IMAGE_BASE_RELOCATION = record
    VirtualAddress: DWord;
    SizeOfBlock: DWord;
  end;

  PIMAGE_BASE_RELOCATION = ^IMAGE_BASE_RELOCATION;

  IMAGE_IMPORT_DESCRIPTOR = record  //missing from Delphi
    OriginalFirstThunk: DWord; //IMAGE_IMPORT_DESCRIPTOR_0: Anonymous  - OriginalFirstThunk is a name which comes from FP
    TimeDateStamp: DWord;
    ForwarderChain: DWord;
    Name: DWord;
    FirstThunk: DWord;
  end;

  IMAGE_IMPORT_BY_NAME = record
    Hint: Word;
    Name: array[Byte] of AnsiChar;
  end;

  TWideCharArray = array[0..2047] of WideChar;

  //This is also called DllMain.
  TLibEntryProc = function(AInst: HINST; AReason: DWord; AReserved: Pointer): Bool; stdcall;


function GetFirstSection(AHeader: PImageNtHeaders): PIMAGESECTIONHEADER;
begin
  Result := PIMAGESECTIONHEADER(UInt64(AHeader) +
                                UInt64(@AHeader^.OptionalHeader) - UInt64(AHeader) +
                                UInt64(AHeader^.FileHeader.SizeOfOptionalHeader));
end;

constructor TDynMemLib.Create;
begin
  inherited Create;
  FInitialized := False;
  FLibHeaders := nil;
  FCodeAddr := nil;
  FImportedLibsAddr := nil;
  FImportedLibsCount := 0;
  FProtectDiscardableSection := True;
  FProtectNonDiscardableSection := True;
  FAttachLibraryOnLoad := True;
  SetLength(FSections, 0);
end;

destructor TDynMemLib.Destroy;
begin
  SetLength(FSections, 0);
  inherited Destroy;
end;

procedure TDynMemLib.SetProtectionFlags(AProtectDiscardableSection, AProtectNonDiscardableSection: Boolean);
begin
  FProtectDiscardableSection := AProtectDiscardableSection;
  FProtectNonDiscardableSection := AProtectNonDiscardableSection;
end;

procedure TDynMemLib.SetTableSections(ALibData: Pointer; AOldHeaders: TImageNtHeaders);   //TImageNtHeaders has two definitions, one for 32-bit and the other, for 64-bit
var
  WorkSection: PIMAGESECTIONHEADER;
  i, n: Integer;
  Size: DWord; //This is SectionAlignment field in IMAGE_OPTIONAL_HEADER structure
  SrcPointer, DestPointer, VAPointer: Pointer;
begin
  WorkSection := GetFirstSection(FLibHeaders);
  n := FLibHeaders^.FileHeader.NumberOfSections;
  SetLength(FSections, n);

  for i := 0 to n - 1 do
  begin
    VAPointer := Pointer(UInt64(FCodeAddr) + UInt64(WorkSection^.VirtualAddress));

    if WorkSection^.SizeOfRawData = 0 then
    begin
      Size := AOldHeaders.OptionalHeader.SectionAlignment;
      if Size > 0 then
      begin
        DestPointer := VirtualAlloc(VAPointer, PtrUInt(Size), MEM_COMMIT, PAGE_EXECUTE_READWRITE);
        FSections[i].Address := DestPointer;
        FSections[i].Size := Size;
        WorkSection^.Misc.PhysicalAddress := UInt64(DestPointer);
        //ZeroMemory(DestPointer, Size); //should not be required, because VirtualAlloc already clears the memory when using MEM_COMMIT
      end;
    end
    else
    begin
      DestPointer := VirtualAlloc(VAPointer, PtrUInt(WorkSection^.SizeOfRawData), MEM_COMMIT, PAGE_EXECUTE_READWRITE);
      FSections[i].Address := DestPointer;
      FSections[i].Size := WorkSection^.SizeOfRawData;
      SrcPointer := Pointer(UInt64(ALibData) + UInt64(WorkSection^.PointerToRawData));

      //Use CopyMemory as the worst case. However, CopyMemory can overrwrite data in an undefined manner.
      //The order of the first to parameters is swapped.
      Move(SrcPointer^, DestPointer^, WorkSection^.SizeOfRawData);
      WorkSection^.Misc.PhysicalAddress := UInt64(DestPointer);
    end;

    WorkSection := Pointer(UInt64(WorkSection) + UInt64(SizeOf(TIMAGESECTIONHEADER)));
  end;
end;

procedure TDynMemLib.RelocateImageBase(AAmount: UInt64);
var
  ImageDataDir: PImageDataDirectory;
  BaseRelocationAddress: PIMAGE_BASE_RELOCATION;
  DestPointer, DestPointerWithOffset: Pointer;
  RelocationInfo: PWord;
  i, ChunksCount: PtrInt;
  RelocationType: DWord;
  RelocationOffset: Integer;
begin
  ImageDataDir := @FLibHeaders^.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC];

  if ImageDataDir^.Size > 0 then
  begin
    BaseRelocationAddress := Pointer(UInt64(FCodeAddr) + UInt64(ImageDataDir^.VirtualAddress));

    while BaseRelocationAddress^.VirtualAddress > 0 do
    begin
      DestPointer := Pointer(UInt64(FCodeAddr) + UInt64(BaseRelocationAddress^.VirtualAddress));
      RelocationInfo := Pointer(UInt64(BaseRelocationAddress) + UInt64(IMAGE_SIZEOF_BASE_RELOCATION));
      ChunksCount := (BaseRelocationAddress^.SizeOfBlock - IMAGE_SIZEOF_BASE_RELOCATION) shr 1;

      for i := 0 to ChunksCount - 1 do
      begin
        RelocationType := RelocationInfo^ shr 12;
        if RelocationType = IMAGE_REL_BASED_HIGHLOW then
        begin
          RelocationOffset := RelocationInfo^ and $FFF;
          DestPointerWithOffset := Pointer(UInt64(DestPointer) + UInt64(RelocationOffset));
          PUInt64(DestPointerWithOffset)^ := PUInt64(DestPointerWithOffset)^ + AAmount;
        end;

        Inc(RelocationInfo); //next (pointer) location
      end;

      BaseRelocationAddress := Pointer(UInt64(BaseRelocationAddress) + UInt64(BaseRelocationAddress^.SizeOfBlock));
    end;
  end;
end;

procedure ConvertPAnsiCharToPChar(AAnsi: Pointer; var AWide: TWideCharArray);
begin
  {$IFDEF UNICODE}
    Move(StringToOleStr(PAnsiChar(AAnsi))[0], AWide[0], (High(TWideCharArray) + 1) shl 1);
  {$ELSE}
    Move(PAnsiChar(AAnsi)[0], AWide[0], High(TWideCharArray) + 1);
  {$ENDIF}
end;

procedure TDynMemLib.LoadImports;
var
  ImageDataDir: PImageDataDirectory;
  ImportDescriptor: PIMAGE_IMPORT_DESCRIPTOR;
  LibName: TWideCharArray;
  LibNameAddress: Pointer;
  LibHandle: HModule;
  Temp64: UInt64;
  ThunkRef, FuncRef: PPtrUInt;
  SrcPointer, DestPointer: Pointer;
  ThunkData: IMAGE_IMPORT_BY_NAME;
begin
  ImageDataDir := @FLibHeaders^.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];

  if ImageDataDir^.Size > 0 then
  begin
    ImportDescriptor := Pointer(UInt64(FCodeAddr) + UInt64(ImageDataDir^.VirtualAddress));

    while not IsBadReadPtr(ImportDescriptor, SizeOf(IMAGE_IMPORT_DESCRIPTOR)) and (ImportDescriptor^.Name <> 0) do
    begin
      LibNameAddress := Pointer(UInt64(FCodeAddr) + UInt64(ImportDescriptor^.Name));
      ConvertPAnsiCharToPChar(LibNameAddress, LibName);
      LibHandle := LoadLibrary(@LibName[0]);

      if LibHandle = INVALID_HANDLE_VALUE then
        raise Exception.Create('Cannot load library ' + string(LibName));

      if FImportedLibsAddr = nil then
        FImportedLibsAddr := AllocMem(1);

      FImportedLibsAddr := ReAllocMem(FImportedLibsAddr, PtrUInt((FImportedLibsCount + 1) * SizeOf(UInt64)));

      if FImportedLibsAddr = nil then
        raise Exception.Create('ReAllocMem cannot allocate memory for the library modules. ModulesCount is ' + IntToStr(FImportedLibsCount));

      Temp64 := FImportedLibsCount * SizeOf(UInt64);
      FImportedLibsAddr := Pointer(UInt64(FImportedLibsAddr) + Temp64);
      UInt64(FImportedLibsAddr^) := LibHandle;
      FImportedLibsAddr := Pointer(UInt64(FImportedLibsAddr) - Temp64);
      Inc(FImportedLibsCount);

      if ImportDescriptor^.OriginalFirstThunk <> 0 then
        ThunkRef := Pointer(UInt64(FCodeAddr) + UInt64(ImportDescriptor^.OriginalFirstThunk))
      else
        ThunkRef := Pointer(UInt64(FCodeAddr) + UInt64(ImportDescriptor^.FirstThunk));

      FuncRef := Pointer(UInt64(FCodeAddr) + UInt64(ImportDescriptor^.FirstThunk));

      while ThunkRef^ <> 0 do
      begin
        {$IFDEF FPC}
          if ThunkRef^ and IMAGE_ORDINAL_FLAG <> 0 then
        {$ELSE} //Delphi
          if ((SizeOf(Pointer) = 4) and (ThunkRef^ and IMAGE_ORDINAL_FLAG32 <> 0)) or
             ((SizeOf(Pointer) = 8) and (ThunkRef^ and IMAGE_ORDINAL_FLAG64 <> 0)) then
        {$ENDIF}
            FuncRef^ := UInt64(GetProcAddress(LibHandle, PAnsiChar(ThunkRef^ and $0000FFFF)))
          else
          begin
            SrcPointer := Pointer(UInt64(FCodeAddr) + UInt64(ThunkRef^));
            DestPointer := @ThunkData;
            Move(SrcPointer^, DestPointer^, SizeOf(IMAGE_IMPORT_BY_NAME));
            FuncRef^ := UInt64(GetProcAddress(LibHandle, PAnsiChar(@ThunkData.Name)));
          end;

        if FuncRef^ = 0 then
          raise Exception.Create('GetProcAddress cannot get address while creating import table, at ModuleIndex ' + IntToStr(FImportedLibsCount) + ' and function ' + string(@ThunkData.Name) + '.');

        Inc(FuncRef);
        Inc(ThunkRef);
      end;

      ImportDescriptor := Pointer(UInt64(ImportDescriptor) + UInt64(SizeOf(IMAGE_IMPORT_DESCRIPTOR)));
    end;
  end;
end;

function GetSectionProtectionInfo(ACharacteristics: DWord): DWord;
begin
  Result := 0;
  if ACharacteristics and IMAGE_SCN_MEM_NOT_CACHED > 0 then
    Result := Result or PAGE_NOCACHE;

  if ACharacteristics and IMAGE_SCN_MEM_EXECUTE > 0 then
  begin
    //with execute flag
    if ACharacteristics and IMAGE_SCN_MEM_READ > 0 then
    begin
      //with read flag
      if ACharacteristics and IMAGE_SCN_MEM_WRITE > 0 then
        Result := Result or PAGE_EXECUTE_READWRITE
      else
        Result := Result or PAGE_EXECUTE_READ
    end
    else
    begin
      //without read flag
      if ACharacteristics and IMAGE_SCN_MEM_WRITE > 0 then
        Result := Result or PAGE_EXECUTE_WRITECOPY
      else
        Result := Result or PAGE_EXECUTE
    end
  end
  else
  begin
    //without execute flag
    if ACharacteristics and IMAGE_SCN_MEM_READ > 0 then
    begin
      //with read flag
      if ACharacteristics and IMAGE_SCN_MEM_WRITE > 0 then
        Result := Result or PAGE_READWRITE
      else
        Result := Result or PAGE_READONLY;
    end
    else
    begin
      //without read flag
      if ACharacteristics and IMAGE_SCN_MEM_WRITE > 0 then
        Result := Result or PAGE_WRITECOPY
      else
        Result := Result or PAGE_NOACCESS;
    end;
  end;
end;

procedure TDynMemLib.ProtectTableSections;
var
  WorkSection: PIMAGESECTIONHEADER;
  i, n: Integer;
  ProtectionInfo, OldProtectionInfo, DataSize: DWord;
begin
  WorkSection := GetFirstSection(FLibHeaders);
  n := FLibHeaders^.FileHeader.NumberOfSections;

  for i := 0 to n - 1 do
  begin
    if FProtectDiscardableSection and (WorkSection^.Characteristics and IMAGE_SCN_MEM_DISCARDABLE > 0) then
    begin
      VirtualFree(Pointer(WorkSection^.Misc.PhysicalAddress), PtrUInt(WorkSection^.SizeOfRawData), MEM_DECOMMIT);
      WorkSection := Pointer(UInt64(WorkSection) + UInt64(SizeOf(TIMAGESECTIONHEADER)));
      Continue;
    end;

    if FProtectNonDiscardableSection and (WorkSection^.Characteristics and IMAGE_SCN_MEM_DISCARDABLE = 0) then
    begin
      ProtectionInfo := GetSectionProtectionInfo(WorkSection^.Characteristics);
      if WorkSection^.Characteristics and IMAGE_SCN_MEM_NOT_CACHED > 0 then
        ProtectionInfo := ProtectionInfo or PAGE_NOCACHE;

      DataSize := WorkSection^.SizeOfRawData;
      if DataSize = 0 then
      begin
        if WorkSection^.Characteristics and IMAGE_SCN_CNT_INITIALIZED_DATA > 0 then
          DataSize := FLibHeaders^.OptionalHeader.SizeOfInitializedData
        else
          if WorkSection^.Characteristics and IMAGE_SCN_CNT_UNINITIALIZED_DATA > 0 then
            DataSize := FLibHeaders^.OptionalHeader.SizeOfUninitializedData;

        if DataSize > 0 then
          if not VirtualProtect(Pointer(WorkSection^.Misc.PhysicalAddress), WorkSection^.SizeOfRawData, ProtectionInfo, OldProtectionInfo) then //OldProtectionInfo has to be a valid var
            Exit;//raise Exception.Create('VirtualProtect cannot set protection info at section ' + IntToStr(i) + ' of ' + IntToStr(n) + '.');
      end;
    end;

    WorkSection := Pointer(UInt64(WorkSection) + UInt64(SizeOf(TIMAGESECTIONHEADER)));
  end;
end;

function TDynMemLib.MemLoadLibrary(ALibData: Pointer): Boolean;
var
  DosHeader: TIMAGEDOSHEADER;
  OldHeader: TImageNtHeaders;
  HeaderAddress, CodeAddress: Pointer;
  LocationAmount: UInt64;
  LibEntryProc: TLibEntryProc;
begin
  Result := False;

  try
    Move(ALibData^, DosHeader, SizeOf(IMAGE_DOS_HEADER));
    if DosHeader.e_magic <> IMAGE_DOS_SIGNATURE then
      raise Exception.Create('Invalid DOS header in library.');

    HeaderAddress := Pointer(UInt64(ALibData) + UInt64(DosHeader._lfanew));
    Move(HeaderAddress^, OldHeader, SizeOf(IMAGE_NT_HEADERS));

    if OldHeader.Signature <> IMAGE_NT_SIGNATURE then
      raise Exception.Create('Invalid IMAGE_NT_SIGNATURE value.');

    CodeAddress := VirtualAlloc(Pointer(OldHeader.OptionalHeader.ImageBase),
                                PtrUInt(OldHeader.OptionalHeader.SizeOfImage),
                                MEM_RESERVE,
                                PAGE_EXECUTE_READWRITE);

    if CodeAddress = nil then
      CodeAddress := VirtualAlloc(nil,
                                  PtrUInt(OldHeader.OptionalHeader.SizeOfImage),
                                  MEM_RESERVE,
                                  PAGE_EXECUTE_READWRITE);

    if CodeAddress = nil then
      raise Exception.Create('Cannot allocate memory with VirtualAlloc for library code.');

    FCodeAddr := CodeAddress;
    FImportedLibsCount := 0;
    FImportedLibsAddr := nil;

    VirtualAlloc(CodeAddress, PtrUInt(OldHeader.OptionalHeader.SizeOfImage), MEM_COMMIT, PAGE_EXECUTE_READWRITE);   //Check result?
    HeaderAddress := VirtualAlloc(CodeAddress, PtrUInt(OldHeader.OptionalHeader.SizeOfHeaders), MEM_COMMIT, PAGE_EXECUTE_READWRITE);
    Move(ALibData^, HeaderAddress^, UInt64(DosHeader._lfanew) + UInt64(OldHeader.OptionalHeader.SizeOfHeaders));

    FLibHeaders := PImageNtHeaders(UInt64(HeaderAddress) + UInt64(DosHeader._lfanew));
    FLibHeaders^.OptionalHeader.ImageBase := PtrUInt(CodeAddress);
    SetTableSections(ALibData, OldHeader);

    LocationAmount := UInt64(CodeAddress) - UInt64(OldHeader.OptionalHeader.ImageBase);
    if LocationAmount <> 0 then
      RelocateImageBase(LocationAmount);

    try
      LoadImports;
    except
      on E: Exception do
        raise Exception.Create('Cannot load library imports. ' + E.Message);
    end;

    ProtectTableSections;
    if FLibHeaders^.OptionalHeader.AddressOfEntryPoint > 0 then
    begin
      @LibEntryProc := Pointer(UInt64(CodeAddress) + UInt64(FLibHeaders^.OptionalHeader.AddressOfEntryPoint));
      if @LibEntryProc = nil then
        raise Exception.Create('Cannot get library entry point.');

      if FAttachLibraryOnLoad then
        if not LibEntryProc(UInt64(CodeAddress), DLL_PROCESS_ATTACH, nil) then
          raise Exception.Create('Cannot attach library.');

      FInitialized := True;
    end;
  except
    on E: Exception do
    begin
      MemFreeLibrary;
      raise
    end;
  end;

  Result := True;
end;

function TDynMemLib.MemGetProcAddress(AFuncName: PChar): Pointer;
var
  Index, i: Integer;
  ImageDataDir: PImageDataDirectory;
  ExportsDir: PIMAGE_EXPORT_DIRECTORY;
  NameRef: PDWord;
  Ordinal: PWord;
  WideName: TWideCharArray;
  FuncsAddr, CodeAddrWithFuncsAddr: Pointer;
begin
  Result := nil;
  Index := -1;

  ImageDataDir := @FLibHeaders^.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT];
  if ImageDataDir^.Size = 0 then
    raise Exception.Create('Library has no export table.');

  ExportsDir := Pointer(UInt64(FCodeAddr) + UInt64(ImageDataDir^.VirtualAddress));
  if (ExportsDir^.NumberOfNames = 0) or (ExportsDir^.NumberOfFunctions = 0) then
    raise Exception.Create('Library has no exports');

  NameRef := Pointer(UInt64(FCodeAddr) + UInt64(ExportsDir^.AddressOfNames));
  Ordinal := Pointer(UInt64(FCodeAddr) + UInt64(ExportsDir^.AddressOfNameOrdinals));

  for i := 0 to ExportsDir^.NumberOfNames - 1 do
  begin
    ConvertPAnsiCharToPChar(Pointer(UInt64(FCodeAddr) + NameRef^), WideName);
    if StrComp(AFuncName, PChar(@WideName[0])) = 0 then
    begin
      Index := Ordinal^;
      Break;
    end;

    Inc(NameRef);
    Inc(Ordinal);
  end;

  if Index = -1 then
    raise Exception.Create('Cannot find exported symbol.');

  if DWord(Index) > ExportsDir^.NumberOfFunctions - 1 then
    raise Exception.Create('Mismatch between names and function count.');

  FuncsAddr := Pointer(UInt64(ExportsDir^.AddressOfFunctions) + Index shl 2);
  CodeAddrWithFuncsAddr := Pointer(UInt64(FCodeAddr) + UInt64(FuncsAddr));
  Result := Pointer(UInt64(FCodeAddr) + UInt64(PDWord(CodeAddrWithFuncsAddr)^));  //This is PDWord, because dereferencing an 8-byte pointer, results in an invalid offset for 64-bit OS.
end;

function TDynMemLib.MemGetProcAddress(AFuncName: string): Pointer; overload;
begin
  Result := MemGetProcAddress(PChar(@AFuncName[1]));
end;

procedure TDynMemLib.MemFreeLibrary;
var
  i: PtrInt;
  LibEntryProc: TLibEntryProc;
  Temp64: UInt64;
begin
  if FInitialized then
  begin
    if FLibHeaders^.OptionalHeader.AddressOfEntryPoint > 0 then  //not all libraries implement this entry point function
    begin
      @LibEntryProc := Pointer(UInt64(FCodeAddr) + UInt64(FLibHeaders^.OptionalHeader.AddressOfEntryPoint));
      if @LibEntryProc = nil then
        raise Exception.Create('Cannot get library entry point.');

      try
        //This call is limited to 32-bit because it crashes on 64-bit.
        {$IFNDEF CPU64}  //This has to be verified on Delphi 64-bit.
          LibEntryProc(UInt64(FCodeAddr), DLL_PROCESS_DETACH, nil); //Do not verify the result, because the library sets it.
        {$ENDIF}
      except
        on E: Exception do
          raise Exception.Create('Cannot call library entry proc for detaching. ' + E.Message);
      end;
    end;

    FInitialized := False;

    for i := 0 to FImportedLibsCount - 1 do
    begin
      Temp64 := i * SizeOf(UInt64);  //This is how it is allocated (multiple by 8) in LoadImports
      FImportedLibsAddr := Pointer(UInt64(FImportedLibsAddr) + UInt64(Temp64));
      if UInt64(FImportedLibsAddr^) <> INVALID_HANDLE_VALUE then
        FreeLibrary(UInt64(FImportedLibsAddr^));

      FImportedLibsAddr := Pointer(UInt64(FImportedLibsAddr) - UInt64(Temp64));
    end;

    FreeMemory(FImportedLibsAddr); //Free memory, which has been allocated in LoadImports with AllocMem and ReallocMem

    if FCodeAddr <> nil then
      VirtualFree(FCodeAddr, 0, MEM_RELEASE);

    FImportedLibsAddr := nil;

    for i := 0 to Length(FSections) - 1 do
      if FSections[i].Address <> nil then
        VirtualFree(FSections[i].Address, FSections[i].Size, MEM_RELEASE);
  end;
end;

end.

